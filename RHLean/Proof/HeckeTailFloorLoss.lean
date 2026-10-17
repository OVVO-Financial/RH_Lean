import Mathlib

/-!
# Hecke eighth-root tail floor loss

This module isolates the exact numerical step in claim
`20261017-referee-1`. The arithmetic estimate for the genuine
`BAD_y(X)` carrier remains a paper theorem; it is represented here by the
explicit `hbad` premise. The conclusion certifies that the floor at
`y = floor(X^(1/8))` costs at most a factor `3/2` once `X >= 256`.

No bound on the signed Hecke core is asserted.
-/

namespace RHLean.Proof

/-- If `y >= 2` and `z < y + 1`, then the factor `2 z / y` is at most
`3`. For `y = floor z`, these are exactly the upper floor-window and
large-enough-cutoff facts used in the eighth-root tail estimate. -/
theorem heckeEighthRoot_floorLoss_le_three
    {z : ℝ} {y : ℕ} (hy : 2 ≤ y) (hz : z < (y : ℝ) + 1) :
    2 * z / (y : ℝ) ≤ 3 := by
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyPos : (0 : ℝ) < (y : ℝ) := by linarith
  apply (div_le_iff₀ hyPos).2
  nlinarith

/-- Conditional consumer for the accepted Hecke tail estimate.

Set `z = X^(1/8)`, `y = floor z`, and
`scale = X^(7/8) * (1 + log X)`. The paper bound
`badMagnitude <= 2 * z / y * scale` then sharpens from constant `4`
to constant `3`. The arithmetic proof of that premise is deliberately
not hidden in this theorem. -/
theorem heckeBad_le_three_mul_scale_of_base
    {badMagnitude scale z : ℝ} {y : ℕ}
    (hscale : 0 ≤ scale) (hy : 2 ≤ y) (hz : z < (y : ℝ) + 1)
    (hbad : badMagnitude ≤ (2 * z / (y : ℝ)) * scale) :
    badMagnitude ≤ 3 * scale := by
  exact hbad.trans
    (mul_le_mul_of_nonneg_right
      (heckeEighthRoot_floorLoss_le_three hy hz) hscale)

end RHLean.Proof
