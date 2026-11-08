import «research.oai_434.VF919ExplicitFixedSourceSlotCount»
import «research.oai_434.VF919TotalMassEndpoint»

/-!
# Explicit finite-slot consequences of the complete total-mass endpoint

The existing explicit source has `N = explicitSlotCount` and every slot
length at least `1 / (12 * N)`.  The complete total-mass theorem consumes
that very source and supplies one quarter of its actual minimum as a
global zero-boundary saving.  Their composition gives `1 / (48 * N)`.

The Mertens growth theorem keeps every positive exponent loss.  The fixed
power theorem spends exactly half the saving.  All constants are chosen
before the integer cutoff; no new source bound or desired conclusion is
assumed.
-/

namespace OAI.SevenEighths.RHLeanExplicitSlotTotalMass

open Parameters

/-- The explicit source uses a positive, fixed natural number of slots. -/
theorem slot_count_pos : 0 < explicitSlotCount := by
  have h := explicitSlotCount_two_le
  omega

/-- Positivity of the same count in the real exponent formulas. -/
theorem slot_count_cast_pos : 0 < (explicitSlotCount : ℝ) := by
  exact_mod_cast slot_count_pos

/-- The full total-mass saving is strictly positive. -/
theorem saving_pos :
    0 < (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) := by
  exact div_pos zero_lt_one (mul_pos (by norm_num) slot_count_cast_pos)

/-- Half of the saving can be spent on a fixed Mertens power bound. -/
theorem fixed_saving_pos :
    0 < (1 : ℝ) / (96 * (explicitSlotCount : ℝ)) := by
  exact div_pos zero_lt_one (mul_pos (by norm_num) slot_count_cast_pos)

/-- A simple upper bound suffices to keep the explicit boundary above one half. -/
theorem saving_le_one_ninety_sixth :
    (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) ≤ 1 / 96 := by
  have hN : (2 : ℝ) ≤ (explicitSlotCount : ℝ) := by
    exact_mod_cast explicitSlotCount_two_le
  exact div_le_div_of_nonneg_left zero_le_one (by norm_num)
    (by linarith only [hN])

/-- The explicit every-positive-loss boundary is in the Mertens transfer range. -/
theorem half_le_growth_boundary :
    (1 / 2 : ℝ) ≤ 7 / 8 - (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) := by
  linarith only [saving_le_one_ninety_sixth]

/-- The finite slot construction gives a strict improvement below seven eighths. -/
theorem growth_boundary_lt_seven_eighths :
    (7 / 8 : ℝ) - (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) < 7 / 8 := by
  linarith only [saving_pos]

/-- The explicit boundary is strictly sublinear. -/
theorem growth_boundary_lt_one :
    (7 / 8 : ℝ) - (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) < 1 := by
  linarith only [growth_boundary_lt_seven_eighths]

/-- Spending half the saving still leaves the fixed exponent above one half. -/
theorem half_le_fixed_boundary :
    (1 / 2 : ℝ) ≤ 7 / 8 - (1 : ℝ) / (96 * (explicitSlotCount : ℝ)) := by
  have hhalf :
      (1 : ℝ) / (96 * (explicitSlotCount : ℝ)) =
        ((1 : ℝ) / (48 * (explicitSlotCount : ℝ))) / 2 := by
    ring
  rw [hhalf]
  linarith only [saving_le_one_ninety_sixth]

/-- The fixed exponent is also strictly sublinear. -/
theorem fixed_boundary_lt_one :
    (7 / 8 : ℝ) - (1 : ℝ) / (96 * (explicitSlotCount : ℝ)) < 1 := by
  linarith only [fixed_saving_pos]

/-- The total-mass construction multiplies the old explicit saving by six. -/
theorem gain_is_six_times_old :
    (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) =
      6 * ((1 : ℝ) / (288 * (explicitSlotCount : ℝ))) := by
  ring

end OAI.SevenEighths.RHLeanExplicitSlotTotalMass

namespace OAI.SevenEighths

open Parameters RHLeanActualSlotMin

/-- Apply the complete endpoint to the existing explicit finite source. -/
theorem native_beta_le_explicit_slot_count_total_mass :
    HeckeZeroSupremum.beta ≤
      (7 / 8 : ℝ) - (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) := by
  obtain ⟨D, hfine, hslotLower, _hN, _ht⟩ := exists_explicit_high_data_fine
  have hbound := native_beta_le_true_physical_slot_minimum_total_mass_of_fine D hfine
  have hmin : (1 : ℝ) / (12 * (explicitSlotCount : ℝ)) ≤ actualSlotMinimum D :=
    hslotLower (leastSlotIndex D)
  have hident : (1 : ℝ) / (48 * (explicitSlotCount : ℝ)) =
      ((1 : ℝ) / (12 * (explicitSlotCount : ℝ))) / 4 := by
    ring
  rw [hident]
  linarith only [hbound, hmin]

#print axioms native_beta_le_explicit_slot_count_total_mass

end OAI.SevenEighths

namespace RHLean.Analysis

open MertensExponent OAI.SevenEighths
open Parameters RHLeanNativeSevenEighthsReplay RHLeanExplicitSlotTotalMass

/-- The exact native Mertens transfer at the explicit total-mass boundary. -/
theorem native_mertens_explicit_slot_count_total_mass :
    MertensGrowthAtMost
      ((7 / 8 : ℝ) - (1 : ℝ) / (48 * (explicitSlotCount : ℝ))) := by
  exact growthAtMost_mono native_beta_le_explicit_slot_count_total_mass
    native_mertens_growth_at_hecke_beta

/-- A fixed power envelope, after explicitly spending half the saving. -/
theorem native_mertens_fixed_explicit_slot_count_total_mass :
    MertensExponent.MertensPowerBound
      ((7 / 8 : ℝ) - (1 : ℝ) / (96 * (explicitSlotCount : ℝ))) := by
  convert native_mertens_explicit_slot_count_total_mass
    ((1 : ℝ) / (96 * (explicitSlotCount : ℝ))) fixed_saving_pos using 1
  ring

#print axioms native_mertens_explicit_slot_count_total_mass
#print axioms native_mertens_fixed_explicit_slot_count_total_mass

end RHLean.Analysis
