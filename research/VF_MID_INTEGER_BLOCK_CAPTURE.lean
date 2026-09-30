import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»

/-!
# Integer VF-mid square-block capture

The analytic midpoint construction uses the real cumulative level

  F_R = vfMidFinishedMass R.

For comparison with the integer-valued prime-counting staircase, the natural
square-block level is its natural floor

  K_R = floor(F_R).

This file formalizes the exact floor sandwich and the elementary consequence
of square-block capture.  No PNT-rate input is used.

The prime block convention is the repository's direct convention

  (R^2, (R+1)^2],

which has the same prime population as the open interior because the upper
square is composite for R >= 2.
-/

noncomputable section

namespace RHLean.Analysis

/-- One complete midpoint mass is nonnegative on the live square range. -/
theorem vfMidBandMass_nonneg_of_two_le (r : ℕ) (hr : 2 ≤ r) :
    0 ≤ vfMidBandMass r := by
  unfold vfMidBandMass vfMidBandMidpoint
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hr
  have hm : (1 : ℝ) < (r : ℝ) ^ 2 + (r : ℝ) + 1 / 2 := by
    nlinarith
  have hlog :
      0 < Real.log ((r : ℝ) ^ 2 + (r : ℝ) + 1 / 2) :=
    Real.log_pos hm
  exact div_nonneg (by positivity) hlog.le

/-- The cumulative midpoint level is nonnegative. -/
theorem vfMidFinishedMass_nonneg (R : ℕ) :
    0 ≤ vfMidFinishedMass R := by
  unfold vfMidFinishedMass
  apply Finset.sum_nonneg
  intro r hr
  exact vfMidBandMass_nonneg_of_two_le r (Finset.mem_Ico.mp hr).1

/-- Integer square-block level attached to the real VF-mid cumulative level. -/
def vfMidIntegerBlockLevel (R : ℕ) : ℕ :=
  ⌊vfMidFinishedMass R⌋₊

/-- The integer level lies below the real cumulative midpoint level. -/
theorem vfMidIntegerBlockLevel_cast_le (R : ℕ) :
    (vfMidIntegerBlockLevel R : ℝ) ≤ vfMidFinishedMass R := by
  unfold vfMidIntegerBlockLevel
  exact Nat.floor_le (vfMidFinishedMass_nonneg R)

/-- The real cumulative midpoint level lies strictly below the next integer. -/
theorem vfMidFinishedMass_lt_integerBlockLevel_add_one (R : ℕ) :
    vfMidFinishedMass R < (vfMidIntegerBlockLevel R : ℝ) + 1 := by
  unfold vfMidIntegerBlockLevel
  simpa using Nat.lt_floor_add_one (vfMidFinishedMass R)

/-- Flooring the VF-mid square-block level costs strictly less than one count. -/
theorem vfMidIntegerBlock_rounding_error (R : ℕ) :
    0 ≤ vfMidFinishedMass R - (vfMidIntegerBlockLevel R : ℝ) ∧
      vfMidFinishedMass R - (vfMidIntegerBlockLevel R : ℝ) < 1 := by
  constructor
  · linarith [vfMidIntegerBlockLevel_cast_le R]
  · linarith [vfMidFinishedMass_lt_integerBlockLevel_add_one R]

/-- The integer VF-mid level is captured by its own square block exactly when it
lies between the prime-count values at the two consecutive square endpoints. -/
def VFMidIntegerBlockCaptured (R : ℕ) : Prop :=
  Nat.primeCounting (R ^ 2) ≤ vfMidIntegerBlockLevel R ∧
    vfMidIntegerBlockLevel R ≤ Nat.primeCounting ((R + 1) ^ 2)

/-- Universal immediate square-block capture statement. -/
def VFMidIntegerBlockCaptureStatement : Prop :=
  ∀ R : ℕ, 2 ≤ R → VFMidIntegerBlockCaptured R

/-- The prime-count increment across one square block is at most the number of
interior sites, namely 2R. -/
theorem vfMidSquareBand_primeCounting_increment_le_two_mul (R : ℕ) :
    Nat.primeCounting ((R + 1) ^ 2) ≤
      Nat.primeCounting (R ^ 2) + 2 * R := by
  have hp := vfMidSquareBand_prime_card_add_primeCounting_sq R
  have hsites := vfMidSquareBand_prime_card_add_composite_card R
  omega

/-- Immediate integer-block capture traps the real VF-mid square-endpoint
discrepancy inside one square-block width, plus the sub-unit flooring error. -/
theorem vfMidIntegerBlockCaptured_abs_squareEndpointError_lt
    (R : ℕ) (hcap : VFMidIntegerBlockCaptured R) :
    |vfMidSquareEndpointError R| < 2 * (R : ℝ) + 1 := by
  rcases hcap with ⟨hlow, hupp⟩
  have hKleF := vfMidIntegerBlockLevel_cast_le R
  have hFlt := vfMidFinishedMass_lt_integerBlockLevel_add_one R
  have hlowR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (vfMidIntegerBlockLevel R : ℝ) := by
    exact_mod_cast hlow
  have huppR :
      (vfMidIntegerBlockLevel R : ℝ) ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hupp
  have hprime :=
    vfMidSquareBand_primeCounting_increment_le_two_mul R
  have hprimeR :
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) + 2 * (R : ℝ) := by
    exact_mod_cast hprime
  have hnonpos :
      vfMidSquareEndpointError R ≤ 0 := by
    unfold vfMidSquareEndpointError
    linarith
  have hlower :
      -(2 * (R : ℝ) + 1) < vfMidSquareEndpointError R := by
    unfold vfMidSquareEndpointError
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- The square-endpoint coordinate in the composite bridge is exactly the
existing VF-mid prime error at the same square. -/
theorem vfMidSquareEndpointError_eq_primeError
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError R =
      vfMidPrimeError ((R : ℝ) ^ 2) := by
  unfold vfMidSquareEndpointError vfMidPrimeError
  rw [vfMid_sq hR]
  have hfloor : ⌊(R : ℝ) ^ 2⌋₊ = R ^ 2 := by
    rw [show (R : ℝ) ^ 2 = ((R ^ 2 : ℕ) : ℝ) by norm_num]
    exact Nat.floor_natCast (R ^ 2)
  unfold vfMidPrimeCount
  rw [hfloor]

/-- If every integer VF-mid level is captured in its own square block, then the
open VF-mid square-endpoint von-Koch target follows with an explicit constant. -/
theorem vfMidSquareEndpointVonKochBounded_of_integerBlockCapture
    (hcap : VFMidIntegerBlockCaptureStatement) :
    VFMidSquareEndpointVonKochBoundedStatement := by
  let C : ℝ := 3 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  have herr :=
    vfMidIntegerBlockCaptured_abs_squareEndpointError_lt R (hcap R hR)
  have hEq := vfMidSquareEndpointError_eq_primeError R hR
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hR
  have hlogR : Real.log 2 ≤ Real.log (R : ℝ) := by
    exact Real.log_le_log (by norm_num) hRreal
  have hscale :
      2 * (R : ℝ) + 1 ≤ C * (R : ℝ) * Real.log (R : ℝ) := by
    have hthree : 2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := by
      linarith
    have hratio : 1 ≤ Real.log (R : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      simpa using hlogR
    dsimp [C]
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    calc
      2 * (R : ℝ) + 1 ≤ 3 * (R : ℝ) := hthree
      _ ≤ 3 * (R : ℝ) *
            (Real.log (R : ℝ) / Real.log 2) := by
          nlinarith
      _ = (3 / Real.log 2) * (R : ℝ) * Real.log (R : ℝ) := by
          field_simp [hlog2.ne']
          ring
  rw [← hEq]
  exact le_trans (le_of_lt herr) hscale

/-- Universal integer-block capture therefore closes the repository's
von-Koch/RH consumer. -/
theorem riemannHypothesis_of_vfMidIntegerBlockCapture
    (criterion : ClassicalVonKochRHCriterion)
    (hcap : VFMidIntegerBlockCaptureStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_integerBlockCapture hcap)

/-! ## Delayed block capture

Immediate capture is stronger than necessary and has small finite exceptions.
The useful relaxed object asks only that K_R be reached by the end of a later
square block.
-/

/-- K_R is reached no later than the end of the block with lag L.
L = 0 is immediate capture; L = 1 allows the following square block. -/
def VFMidIntegerBlockCapturedByLag (R L : ℕ) : Prop :=
  Nat.primeCounting (R ^ 2) ≤ vfMidIntegerBlockLevel R ∧
    vfMidIntegerBlockLevel R ≤ Nat.primeCounting ((R + L + 1) ^ 2)

/-- Site-count bound from R^2 to the endpoint of a lag-L capture window. -/
theorem vfMid_primeCounting_lag_window_le
    (R L : ℕ) :
    Nat.primeCounting ((R + L + 1) ^ 2) ≤
      Nat.primeCounting (R ^ 2) +
        ((R + L + 1) ^ 2 - R ^ 2) := by
  have hsq : R ^ 2 ≤ (R + L + 1) ^ 2 := by
    nlinarith
  have h :=
    vfMid_primeCounting_add_le
      (R ^ 2) ((R + L + 1) ^ 2 - R ^ 2)
  rw [Nat.add_sub_of_le hsq] at h
  exact h

/-- Delayed capture gives an exact deterministic endpoint bound by the number
of integer sites traversed, plus the sub-unit flooring error. -/
theorem vfMidIntegerBlockCapturedByLag_abs_squareEndpointError_lt
    (R L : ℕ) (hcap : VFMidIntegerBlockCapturedByLag R L) :
    |vfMidSquareEndpointError R| <
      (((R + L + 1) ^ 2 - R ^ 2 : ℕ) : ℝ) + 1 := by
  rcases hcap with ⟨hlow, hupp⟩
  have hKleF := vfMidIntegerBlockLevel_cast_le R
  have hFlt := vfMidFinishedMass_lt_integerBlockLevel_add_one R
  have hlowR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (vfMidIntegerBlockLevel R : ℝ) := by
    exact_mod_cast hlow
  have huppR :
      (vfMidIntegerBlockLevel R : ℝ) ≤
        (Nat.primeCounting ((R + L + 1) ^ 2) : ℝ) := by
    exact_mod_cast hupp
  have hprime := vfMid_primeCounting_lag_window_le R L
  have hprimeR :
      (Nat.primeCounting ((R + L + 1) ^ 2) : ℝ) ≤
        (Nat.primeCounting (R ^ 2) : ℝ) +
          (((R + L + 1) ^ 2 - R ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hprime
  have hnonpos :
      vfMidSquareEndpointError R ≤ 0 := by
    unfold vfMidSquareEndpointError
    linarith
  have hlower :
      -((((R + L + 1) ^ 2 - R ^ 2 : ℕ) : ℝ) + 1) <
        vfMidSquareEndpointError R := by
    unfold vfMidSquareEndpointError
    linarith
  rw [abs_of_nonpos hnonpos]
  linarith

/-- The empirically observed one-block-delay variant has a purely linear
deterministic consequence. -/
theorem vfMidIntegerBlockCapturedByOneLag_abs_squareEndpointError_lt
    (R : ℕ) (hcap : VFMidIntegerBlockCapturedByLag R 1) :
    |vfMidSquareEndpointError R| < 4 * (R : ℝ) + 5 := by
  have h :=
    vfMidIntegerBlockCapturedByLag_abs_squareEndpointError_lt R 1 hcap
  have hsq : R ^ 2 ≤ (R + 2) ^ 2 := by nlinarith
  have hcast :
      ((((R + 2) ^ 2 - R ^ 2 : ℕ) : ℝ) + 1) =
        4 * (R : ℝ) + 5 := by
    rw [Nat.cast_sub hsq]
    push_cast
    ring
  have hrewrite :
      ((R + 1 + 1) ^ 2 - R ^ 2 : ℕ) = (R + 2) ^ 2 - R ^ 2 := by
    omega
  rw [hrewrite, hcast] at h
  exact h

end RHLean.Analysis
