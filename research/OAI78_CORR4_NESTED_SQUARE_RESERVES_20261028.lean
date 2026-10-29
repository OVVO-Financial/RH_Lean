import Mathlib
import «research.CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026»

/-!
# CORR-4 nested finite-C exact square completion and saturation reserves

This exact real-algebra theorem keeps the complete signed parent and genuine
reciprocal daughter column. The nonnegative reserves are explicit. The
coefficient 9/8 exceeds 1: the result DOES NOT prove a contraction or RH.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

/-- Exact CORR-4 square completion at the reciprocal frame coefficient 1/4. -/
theorem oai78Nested_square_completion
    (parent reciprocal energy : ℝ) :
    (parent + reciprocal) ^ 2 - (9 / 4 : ℝ) * energy =
      (9 / 8 : ℝ) * parent ^ 2 -
      8 * (reciprocal - parent / 8) ^ 2 -
      (9 / 4 : ℝ) * (energy - 4 * reciprocal ^ 2) := by
  ring

/-- The quarter-frame gives a *nonnegative* second saturation reserve. -/
theorem oai78Nested_frame_defect_nonneg
    (reciprocal energy : ℝ)
    (hframe : reciprocal ^ 2 ≤ (1 / 4 : ℝ) * energy) :
    0 ≤ energy - 4 * reciprocal ^ 2 := by
  nlinarith

/-- Sharp scalar consequence of the two explicit nonnegative reserves.
    This is 9/8 of the parent square, NOT a strict contraction. -/
theorem oai78Nested_square_le_nine_eighths
    (parent reciprocal energy : ℝ)
    (hframe : reciprocal ^ 2 ≤ (1 / 4 : ℝ) * energy) :
    (parent + reciprocal) ^ 2 - (9 / 4 : ℝ) * energy ≤
      (9 / 8 : ℝ) * parent ^ 2 := by
  rw [oai78Nested_square_completion]
  have hres := oai78Nested_frame_defect_nonneg reciprocal energy hframe
  nlinarith [sq_nonneg (reciprocal - parent / 8)]

/-- Source-faithful frame specialization to the original CORR-4
    reciprocal daughter column and its ACTUAL (not model) energy. -/
theorem oai78Nested_original_corr4_square_completion (R : ℕ) :
    (lowOwnerPost789EndpointGapReal R +
      lowOwnerReciprocalMertensColumnReal R) ^ 2 -
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R =
      (9 / 8 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2 -
      8 * (lowOwnerReciprocalMertensColumnReal R -
        lowOwnerPost789EndpointGapReal R / 8) ^ 2 -
      (9 / 4 : ℝ) * (canonicalRoughLowQ2DaughterEnergy R -
        4 * lowOwnerReciprocalMertensColumnReal R ^ 2) := by
  exact oai78Nested_square_completion _ _ _

/-- The original CORR-4 daughter frame even has coefficient 211/900,
    stronger than 1/4. No fake decay claim follows from this algebra. -/
theorem oai78Nested_original_corr4_frame_defect_nonneg (R : ℕ) :
    0 ≤ canonicalRoughLowQ2DaughterEnergy R -
        4 * lowOwnerReciprocalMertensColumnReal R ^ 2 := by
  have hstrong := corr4_reciprocal_column_sq_le_211_900_energy R
  have henergy : 0 ≤ canonicalRoughLowQ2DaughterEnergy R := by
    unfold canonicalRoughLowQ2DaughterEnergy
    apply Finset.sum_nonneg
    intro q _hq
    unfold rawQ2ChildEnergyReal
    positivity
  nlinarith

/-- An unconditional frame upper bound on the actual signed CORR-4
    endpoint-plus-daughter norm. Not a new Mertens exponent. -/
theorem oai78Nested_original_corr4_square_le_nine_eighths (R : ℕ) :
    (lowOwnerPost789EndpointGapReal R +
      lowOwnerReciprocalMertensColumnReal R) ^ 2 -
      (9 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R ≤
      (9 / 8 : ℝ) * lowOwnerPost789EndpointGapReal R ^ 2 := by
  rw [oai78Nested_original_corr4_square_completion]
  have hreserve := oai78Nested_original_corr4_frame_defect_nonneg R
  nlinarith [sq_nonneg (lowOwnerReciprocalMertensColumnReal R -
    lowOwnerPost789EndpointGapReal R / 8)]

#print axioms oai78Nested_square_completion
#print axioms oai78Nested_frame_defect_nonneg
#print axioms oai78Nested_square_le_nine_eighths
#print axioms oai78Nested_original_corr4_square_le_nine_eighths

end RHLean.Proof
