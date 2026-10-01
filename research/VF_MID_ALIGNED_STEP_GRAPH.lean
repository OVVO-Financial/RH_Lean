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


/-! ## Floor sandwich for nonnegative alignment -/

/-- A nonnegative phase preserves nonnegativity of the cumulative VF mass. -/
theorem vfMidAlignedMass_nonneg
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) :
    0 ≤ vfMidAlignedMass c R := by
  unfold vfMidAlignedMass
  exact add_nonneg (vfMidFinishedMass_nonneg R) hc

/-- The aligned integer level lies below the aligned real mass. -/
theorem vfMidAlignedIntegerBlockLevel_cast_le
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) :
    (vfMidAlignedIntegerBlockLevel c R : ℝ) ≤ vfMidAlignedMass c R := by
  unfold vfMidAlignedIntegerBlockLevel
  exact Nat.floor_le (vfMidAlignedMass_nonneg c hc R)

/-- The aligned real mass is strictly below the next integer level. -/
theorem vfMidAlignedMass_lt_integerBlockLevel_add_one
    (c : ℝ) (R : ℕ) :
    vfMidAlignedMass c R <
      (vfMidAlignedIntegerBlockLevel c R : ℝ) + 1 := by
  unfold vfMidAlignedIntegerBlockLevel
  simpa using Nat.lt_floor_add_one (vfMidAlignedMass c R)

/-- Flooring an aligned VF level costs less than one count. -/
theorem vfMidAlignedIntegerBlock_rounding_error
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) :
    0 ≤ vfMidAlignedMass c R -
        (vfMidAlignedIntegerBlockLevel c R : ℝ) ∧
      vfMidAlignedMass c R -
        (vfMidAlignedIntegerBlockLevel c R : ℝ) < 1 := by
  constructor
  · linarith [vfMidAlignedIntegerBlockLevel_cast_le c hc R]
  · linarith [vfMidAlignedMass_lt_integerBlockLevel_add_one c R]

/-! ## Local endpoint bounds from the three graph-intersection modes -/

/-- Horizontal aligned capture gives the same deterministic one-square-width
bound as the unaligned criterion. -/
theorem vfMidAlignedHorizontalCrossed_abs_endpointError_lt
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ)
    (hcross : VFMidAlignedHorizontalCrossed c R) :
    |vfMidAlignedSquareEndpointError c R| < 2 * (R : ℝ) + 2 := by
  rcases hcross with ⟨hlow, hupp⟩
  have hKleF := vfMidAlignedIntegerBlockLevel_cast_le c hc R
  have hFlt := vfMidAlignedMass_lt_integerBlockLevel_add_one c R
  have hlowR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (vfMidAlignedIntegerBlockLevel c R : ℝ) := by
    exact_mod_cast hlow
  have huppR :
      (vfMidAlignedIntegerBlockLevel c R : ℝ) ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hupp
  have hprime :=
    vfMidSquareBand_primeCounting_increment_le_two_mul_add_one R
  have hprimeR :
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) + (2 * (R : ℝ) + 1) := by
    exact_mod_cast hprime
  have hnonpos :
      vfMidAlignedSquareEndpointError c R ≤ 0 := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  have hlower :
      -(2 * (R : ℝ) + 2) <
        vfMidAlignedSquareEndpointError c R := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- A left vertical crossing at x = R^2 traps the aligned endpoint error by
the preceding VF band mass plus the sub-unit flooring error. -/
theorem vfMidAlignedLeftVerticalCrossed_abs_endpointError_lt
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) (hR : 3 ≤ R)
    (hcross : VFMidAlignedLeftVerticalCrossed c R) :
    |vfMidAlignedSquareEndpointError c R| <
      vfMidBandMass (R - 1) + 1 := by
  rcases hcross with ⟨hlow, hupp⟩
  have hpred : 2 ≤ R - 1 := by omega
  have hsucc := vfMidAlignedMass_succ c hpred
  have hpredsucc : R - 1 + 1 = R := by omega
  rw [hpredsucc] at hsucc
  have hprevFlt :=
    vfMidAlignedMass_lt_integerBlockLevel_add_one c (R - 1)
  have hKleF := vfMidAlignedIntegerBlockLevel_cast_le c hc R
  have hlowR :
      (vfMidAlignedIntegerBlockLevel c (R - 1) : ℝ) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) := by
    exact_mod_cast hlow
  have huppR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (vfMidAlignedIntegerBlockLevel c R : ℝ) := by
    exact_mod_cast hupp
  have hnonpos :
      vfMidAlignedSquareEndpointError c R ≤ 0 := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  have hlower :
      -(vfMidBandMass (R - 1) + 1) <
        vfMidAlignedSquareEndpointError c R := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- In the genuinely new right-vertical case, where pi is already above the
current VF level at the left endpoint, the positive aligned discrepancy is at
most one current VF band mass. -/
theorem vfMidAlignedRightVerticalCrossed_abs_endpointError_le_bandMass_of_above
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) (hR : 2 ≤ R)
    (hcross : VFMidAlignedRightVerticalCrossed c R)
    (habove :
      vfMidAlignedIntegerBlockLevel c R <
        Nat.primeCounting (R ^ 2)) :
    |vfMidAlignedSquareEndpointError c R| ≤ vfMidBandMass R := by
  rcases hcross with ⟨_hlow, hupp⟩
  have hgap :
      vfMidAlignedIntegerBlockLevel c R + 1 ≤
        Nat.primeCounting (R ^ 2) := by
    omega
  have hgapR :
      (vfMidAlignedIntegerBlockLevel c R : ℝ) + 1 ≤
        (Nat.primeCounting (R ^ 2) : ℝ) := by
    exact_mod_cast hgap
  have hFlt := vfMidAlignedMass_lt_integerBlockLevel_add_one c R
  have hnonneg :
      0 ≤ vfMidAlignedSquareEndpointError c R := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hmono := Nat.monotone_primeCounting hsq
  have hmonoR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hmono
  have huppR :
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) ≤
        (vfMidAlignedIntegerBlockLevel c (R + 1) : ℝ) := by
    exact_mod_cast hupp
  have hKnext :=
    vfMidAlignedIntegerBlockLevel_cast_le c hc (R + 1)
  have hsucc := vfMidAlignedMass_succ c hR
  have hupper :
      vfMidAlignedSquareEndpointError c R ≤ vfMidBandMass R := by
    unfold vfMidAlignedSquareEndpointError
    linarith
  rw [abs_of_nonneg hnonneg]
  exact hupper

/-- Any right-vertical crossing has a local linear-plus-band bound: if pi has
not yet passed the current level, it is already a horizontal capture; otherwise
the preceding theorem gives the band-mass bound. -/
theorem vfMidAlignedRightVerticalCrossed_abs_endpointError_lt
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) (hR : 2 ≤ R)
    (hcross : VFMidAlignedRightVerticalCrossed c R) :
    |vfMidAlignedSquareEndpointError c R| <
      2 * (R : ℝ) + 2 + vfMidBandMass R := by
  have hmass := vfMidBandMass_nonneg_of_two_le R hR
  by_cases hleft :
      Nat.primeCounting (R ^ 2) ≤ vfMidAlignedIntegerBlockLevel c R
  · have hhorizontal : VFMidAlignedHorizontalCrossed c R :=
      ⟨hleft, hcross.1⟩
    have h :=
      vfMidAlignedHorizontalCrossed_abs_endpointError_lt
        c hc R hhorizontal
    linarith
  · have habove :
        vfMidAlignedIntegerBlockLevel c R <
          Nat.primeCounting (R ^ 2) := by
      omega
    have h :=
      vfMidAlignedRightVerticalCrossed_abs_endpointError_le_bandMass_of_above
        c hc R hR hcross habove
    have hwidth : 0 < 2 * (R : ℝ) + 2 := by positivity
    linarith

/-- Full aligned step-graph crossing on a noninitial square gives an explicit
endpoint bound.  The three summands deliberately keep the proof symmetric and
avoid hiding which graph face supplied the intersection. -/
theorem vfMidAlignedStepGraphCrossed_abs_endpointError_lt
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) (hR : 3 ≤ R)
    (hgraph : VFMidAlignedStepGraphCrossed c R) :
    |vfMidAlignedSquareEndpointError c R| <
      2 * (R : ℝ) + 3 +
        vfMidBandMass R + vfMidBandMass (R - 1) := by
  have hR2 : 2 ≤ R := by omega
  have hpred : 2 ≤ R - 1 := by omega
  have hmass := vfMidBandMass_nonneg_of_two_le R hR2
  have hmassPred := vfMidBandMass_nonneg_of_two_le (R - 1) hpred
  rcases hgraph with hhorizontal | hleft | hright
  · have h :=
      vfMidAlignedHorizontalCrossed_abs_endpointError_lt
        c hc R hhorizontal
    linarith
  · have h :=
      vfMidAlignedLeftVerticalCrossed_abs_endpointError_lt
        c hc R hR hleft
    have hwidth : 0 < 2 * (R : ℝ) + 2 := by positivity
    linarith
  · have h :=
      vfMidAlignedRightVerticalCrossed_abs_endpointError_lt
        c hc R hR2 hright
    linarith

/-- Translating back from the aligned endpoint error to the original VF error
costs only the fixed phase |c|. -/
theorem vfMidDirectSquareEndpointError_abs_lt_of_alignedStepGraphCrossed
    (c : ℝ) (hc : 0 ≤ c) (R : ℕ) (hR : 3 ≤ R)
    (hgraph : VFMidAlignedStepGraphCrossed c R) :
    |vfMidDirectSquareEndpointError R| <
      2 * (R : ℝ) + 3 +
        vfMidBandMass R + vfMidBandMass (R - 1) + |c| := by
  have h :=
    vfMidAlignedStepGraphCrossed_abs_endpointError_lt
      c hc R hR hgraph
  have heq :
      vfMidDirectSquareEndpointError R =
        vfMidAlignedSquareEndpointError c R + c := by
    rw [vfMidAlignedSquareEndpointError_eq_direct_sub]
    ring
  rw [heq]
  calc
    |vfMidAlignedSquareEndpointError c R + c|
        ≤ |vfMidAlignedSquareEndpointError c R| + |c| := abs_add_le _ _
    _ < 2 * (R : ℝ) + 3 +
          vfMidBandMass R + vfMidBandMass (R - 1) + |c| := by
      linarith

/-! ## Deterministic band-mass envelope -/

/-- One midpoint VF band is at most 3R/log(4) for R >= 2.  This is intentionally
crude; only linear scale is needed once graph bracketing is available. -/
theorem vfMidBandMass_le_three_mul_div_log_four
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidBandMass R ≤ 3 * (R : ℝ) / Real.log 4 := by
  unfold vfMidBandMass vfMidBandMidpoint
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hmid4 :
      (4 : ℝ) ≤ (R : ℝ) ^ 2 + (R : ℝ) + 1 / 2 := by
    nlinarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogmid :
      0 < Real.log ((R : ℝ) ^ 2 + (R : ℝ) + 1 / 2) :=
    Real.log_pos (by linarith)
  have hlogle :
      Real.log 4 ≤
        Real.log ((R : ℝ) ^ 2 + (R : ℝ) + 1 / 2) :=
    Real.log_le_log (by norm_num) hmid4
  have hnum :
      2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by
    linarith
  calc
    (2 * (R : ℝ) + 1) /
          Real.log ((R : ℝ) ^ 2 + (R : ℝ) + 1 / 2)
        ≤ (3 * (R : ℝ)) /
          Real.log ((R : ℝ) ^ 2 + (R : ℝ) + 1 / 2) :=
      div_le_div_of_nonneg_right hnum hlogmid.le
    _ ≤ (3 * (R : ℝ)) / Real.log 4 :=
      div_le_div_of_nonneg_left (by positivity) hlog4 hlogle

/-- Universal aligned step-graph bracketing from the first nontrivial
noninitial square onward.  The finitely many earlier squares are irrelevant to
the asymptotic von-Koch consumer and can be absorbed into its constant. -/
def VFMidAlignedStepGraphBracketingStatement (c : ℝ) : Prop :=
  ∀ R : ℕ, 3 ≤ R → VFMidAlignedStepGraphCrossed c R

end RHLean.Analysis
