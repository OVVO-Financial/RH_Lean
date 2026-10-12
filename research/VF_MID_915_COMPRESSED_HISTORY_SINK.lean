import Mathlib

/-!
# #915: exact historical signed-source compression sink

The earlier #915 tests expanded historical signed prime/composite seats into
a huge absolute denominator, yielding an enormous apparent "negative pair
saving." But the PRODUCTION NNS denominator is built from just the
already-compressed signed anchor D_R. There is no independent historical
absolute-value budget.

For an arbitrary historical packet with positive mass HUp and negative
magnitude HLow, and any current absolute mass C, its original compressed
NNS absolute amplitude is

   |HUp-HLow| + C,

whereas full uncompression would use

   HUp+HLow+C.

The exact difference of squared denominators is

  4*HUp*HLow + 4*C*min(HUp,HLow).

Hence the historical opposite-sign pair heat is **already consumed** by
compressing the original denominator. Reusing it as an additional payment
silently counts the same historical cross-pairs twice.

This is an exact algebraic SHARP identity, not a new arithmetic bound.
The correct new owner-variance route keeps D_R compressed while expanding
the CURRENT physical square-block source by centered owner deviations.
-/

namespace RHLean.Analysis

/-- Precise no-free-historical-pair-heat formula. No probabilistic
independence or prime-distribution assumptions. -/
theorem vfMid915HistoryAbsCompression_sq_exact
    (HUp HLow C : ℝ) :
    (HUp + HLow + C)^2 - (|HUp - HLow| + C)^2 =
      4 * HUp * HLow + 4 * C * min HUp HLow := by
  rcases le_total HUp HLow with h | h
  · have hAbs : |HUp - HLow| = HLow - HUp := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    rw [hAbs, min_eq_left h]
    ring
  · have hAbs : |HUp - HLow| = HUp - HLow :=
      abs_of_nonneg (sub_nonneg.mpr h)
    rw [hAbs, min_eq_right h]
    ring

/-- Any fixed signed endpoint target contributes the SAME numerator before
and after rewriting historical packets. The missing absolute-budget sink is
therefore exactly the same positive mixed-sign mass. -/
theorem vfMid915HistoryHalfGateExpansion_leak_exact
    (HUp HLow C endpoint : ℝ) :
    ((HUp + HLow + C)^2 - 2 * endpoint^2) -
        ((|HUp - HLow| + C)^2 - 2 * endpoint^2) =
      4 * HUp * HLow + 4 * C * min HUp HLow := by
  have hnorm := vfMid915HistoryAbsCompression_sq_exact HUp HLow C
  linarith

/-- In actual signed NNS mass currency, the compression sink is nonnegative
whenever historical upper/lower and current absolute masses are nonnegative. -/
theorem vfMid915HistoryAbsCompression_sq_nonneg
    {HUp HLow C : ℝ}
    (hU : 0 ≤ HUp) (hL : 0 ≤ HLow) (hC : 0 ≤ C) :
    0 ≤ (HUp + HLow + C)^2 -
      (|HUp - HLow| + C)^2 := by
  rw [vfMid915HistoryAbsCompression_sq_exact]
  have hmin : 0 ≤ min HUp HLow := le_min hU hL
  have hUL : 0 ≤ HUp * HLow := mul_nonneg hU hL
  have hCM : 0 ≤ C * min HUp HLow := mul_nonneg hC hmin
  nlinarith

/-- This is the "all historical negative pair heat already paid" identity:
an independent off-diagonal payment must come from arithmetic on the
ORIGINAL compressed field, not from inflating its absolute mass. -/
theorem vfMid915CompressedHistoryFrees_no_extra_heat
    (HUp HLow C : ℝ) :
    (HUp + HLow + C)^2 =
      (|HUp - HLow| + C)^2 +
        4 * HUp * HLow + 4 * C * min HUp HLow := by
  have h := vfMid915HistoryAbsCompression_sq_exact HUp HLow C
  linarith

end RHLean.Analysis
