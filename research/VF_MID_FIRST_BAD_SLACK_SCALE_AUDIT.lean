import Mathlib
import «research.VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET»

/-!
# First-bad slack scale audit

This regression module records a currency mismatch which must not be used in
the terminal proof.

The compiled inlet proves a linear estimate

  |Rem_R| < Δ_R,

where

  Δ_R = rho(R+1)^2 - rho(R)^2.

The terminal `hrank` obligation is quadratic.  A bound of the displayed
linear form does not imply `Rem_R^2 <= Δ_R`, even abstractly at the same
scale.  For every R >= 7, Δ_R is already so large that x = Δ_R/2 satisfies

  |x| < Δ_R  but  Δ_R < x^2.

Thus the remainder-slack theorem may be used only as a signed linear residual
fact inside a larger exact identity.  It may not be squared and charged
directly to the one-step radial-square budget.
-/

noncomputable section

namespace RHLean.Analysis

/-- The one-step synthetic radial-square slack. -/
def vfMidFirstBadRadialSquareSlack (R : ℕ) : ℝ :=
  vfMidSyntheticRadialScale (R + 1) ^ 2 -
    vfMidSyntheticRadialScale R ^ 2

/-- From R >= 7 the one-step radial-square slack is already bigger than four. -/
theorem vfMidFirstBadRadialSquareSlack_gt_four
    (R : ℕ) (hR : 7 ≤ R) :
    (4 : ℝ) < vfMidFirstBadRadialSquareSlack R := by
  have h :=
    vfMidSyntheticRadialScale_sq_increment_gt_25_div_3_mul R hR
  unfold vfMidFirstBadRadialSquareSlack
  have hR7 : (7 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hR
  nlinarith

/-- **Regression: linear slack control does not imply quadratic slack control.**

For every admissible scale, there is a scalar strictly inside the very same
linear slack window whose square already exceeds the radial-square slack.
Therefore no proof step may infer a quadratic `hrank` estimate merely from a
bound of the form `|x| < Δ_R`. -/
theorem vfMidFirstBad_linearSlack_does_not_control_square
    (R : ℕ) (hR : 7 ≤ R) :
    ∃ x : ℝ,
      |x| < vfMidFirstBadRadialSquareSlack R ∧
      vfMidFirstBadRadialSquareSlack R < x ^ 2 := by
  let Δ := vfMidFirstBadRadialSquareSlack R
  have hΔ4 : (4 : ℝ) < Δ := by
    simpa [Δ] using vfMidFirstBadRadialSquareSlack_gt_four R hR
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Δ / 2, ?_, ?_⟩
  · rw [abs_of_nonneg (by positivity : 0 ≤ Δ / 2)]
    linarith
  · nlinarith

/-- The actual compiled remainder estimate is only a linear-slack statement.
This corollary deliberately exposes its currency and nothing stronger. -/
theorem abs_vfMidNativeDescentRemainder_lt_firstBadLinearSlack
    (R : ℕ) (hR : 7 ≤ R) :
    |vfMidNativeDescentRemainder R| <
      vfMidFirstBadRadialSquareSlack R := by
  simpa [vfMidFirstBadRadialSquareSlack] using
    abs_vfMidNativeDescentRemainder_lt_radial_sq_increment R hR

end RHLean.Analysis
