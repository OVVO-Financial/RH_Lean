import Mathlib

/-!
# Original OAI low-Gaussian: exact rational budget for the full-J CRT attack

This file proves ONLY rational exponent bookkeeping. It does not prove
the local composite-s Fourier estimate, the marked incidence estimate,
the complete original low detector, or a Mertens exponent improvement.
Source audit: research/OAI_LOW_GAUSSIAN_FULL_J_COMPOSITE_S_DOUBLE_FOURIER_20261025.md
-/

namespace VF919OriginalLowQuadraticBudget

theorem previous_one_ninety_six_deficit :
    (5 / 32 : ℚ) + 1 / 24 - 3 / 16 = 1 / 96 := by
  norm_num

theorem completed_top_j_identity (sigma eta lambda : ℚ) :
    -(17 / 96 : ℚ) +
        (3 / 2 : ℚ) * (1 + sigma + eta) -
        4 * ((1 + sigma + eta) / 3 - lambda) =
      -(1 / 96 : ℚ) + (sigma + eta) / 6 + 4 * lambda := by
  ring

theorem full_j_eighth_example :
    -(1 / 96 : ℚ) + (1 / 8 : ℚ) / 6 = 1 / 96 := by
  norm_num

theorem backup_selected_mark_identity (sigma eta lambda : ℚ) :
    (5 / 32 : ℚ) + sigma / 3 + eta / 3 +
        7 * lambda / 2 + (3 * lambda - sigma) / 2 =
      (5 / 32 : ℚ) - sigma / 6 + eta / 3 + 5 * lambda := by
  ring

theorem backup_selected_mark_eighth_example :
    (5 / 32 : ℚ) - (1 / 8 : ℚ) / 6 = 13 / 96 := by
  norm_num

theorem full_j_range_bookkeeping
    (sigma eta lambda : ℚ)
    (hs : sigma ≤ 1 / 6)
    (he : eta ≤ 1 / 384)
    (hl : lambda ≤ 1 / 384) :
    -(1 / 96 : ℚ) + (sigma + eta) / 6 + 4 * lambda
      ≤ 65 / 2304 := by
  linarith

theorem full_j_range_below_original
    (sigma eta lambda : ℚ)
    (hs : sigma ≤ 1 / 6)
    (he : eta ≤ 1 / 384)
    (hl : lambda ≤ 1 / 384) :
    -(1 / 96 : ℚ) + (sigma + eta) / 6 + 4 * lambda
      ≤ (3 / 16 : ℚ) - 367 / 2304 := by
  have h := full_j_range_bookkeeping sigma eta lambda hs he hl
  linarith

theorem full_j_critical_cutoff (a t : ℚ)
    (ht : (3 / 8 : ℚ) * (1 + a) - 35 / 384 < t) :
    -(17 / 96 : ℚ) + (3 / 2 : ℚ) * (1 + a) - 4 * t
      < 3 / 16 := by
  linarith

theorem full_j_critical_corridor_width (a : ℚ)
    (ha : a ≤ 1 / 6) :
    (1 + a) / 3 - ((3 / 8 : ℚ) * (1 + a) - 35 / 384)
      ≥ 49 / 1152 := by
  linarith

end VF919OriginalLowQuadraticBudget
