import «research.oai_434.VF919ActualSlotMinRetighten»

/-!
# Rational seed directly from the actual finite-slot minimum

The merged exact-minimum source gives a positive but not numerically
evaluated real gap. Here we prove a deterministic RECIPROCAL-INTEGER
sub-gap for every admissible actual-source record.

This is a genuine fixed rational after choosing one source record,
but it is NOT a fully evaluated numeral: the upstream source existence
theorem currently chooses its finite slot count nonconstructively.
Obtaining an a priori numeral requires quantifying that slot constructor.
-/

noncomputable section

namespace OAI.SevenEighths.RHLeanActualSlotMin

open Parameters

/-- One explicit integer denominator for the positive source tilt. -/
def physicalSeedDenominator {Delta : ℝ} (D : HighData Delta) : ℕ :=
  Nat.ceil (24 / actualSlotMinimum D) + 1

theorem physicalSeedDenominator_pos {Delta : ℝ}
    (D : HighData Delta) : 0 < physicalSeedDenominator D := by
  unfold physicalSeedDenominator
  omega

/-- Rational seed is STRICTLY below the true physical tilt. -/
theorem physicalSeedReciprocal_lt_tilt {Delta : ℝ}
    (D : HighData Delta) :
    (1 : ℝ) / (physicalSeedDenominator D : ℝ) <
      actualSlotMinimum D / 24 := by
  have hmin := actualSlotMinimum_pos D
  have hceil : 24 / actualSlotMinimum D <
      (physicalSeedDenominator D : ℝ) := by
    unfold physicalSeedDenominator
    have h := Nat.le_ceil (24 / actualSlotMinimum D)
    push_cast
    linarith only [h]
  have hmul : (24 : ℝ) <
      (physicalSeedDenominator D : ℝ) * actualSlotMinimum D :=
    (div_lt_iff₀ hmin).mp hceil
  have hn : (0 : ℝ) < (physicalSeedDenominator D : ℝ) := by
    exact_mod_cast physicalSeedDenominator_pos D
  apply (div_lt_div_iff₀ hn (by norm_num : (0 : ℝ) < 24)).mpr
  nlinarith only [hmul]

end OAI.SevenEighths.RHLeanActualSlotMin

namespace RHLean.Analysis

open MertensExponent
open OAI.SevenEighths.RHLeanActualSlotMin

/-- A fixed reciprocal-integer improvement on the true Mertens exponent,
from the original analytic source. No arithmetic owner estimate is assumed. -/
theorem native_mertens_reciprocal_integer_seed :
    ∃ D : OAI.SevenEighths.Parameters.HighData (1 / 1000000 : ℝ),
      0 < physicalSeedDenominator D ∧
      MertensGrowthAtMost
        (7 / 8 - (1 : ℝ) / (physicalSeedDenominator D : ℝ)) := by
  obtain ⟨D, hD, hgrowth⟩ := native_mertens_true_physical_slot_minimum
  have hbound : 7 / 8 - actualSlotMinimum D / 24 ≤
      7 / 8 - (1 : ℝ) / (physicalSeedDenominator D : ℝ) := by
    linarith only [physicalSeedReciprocal_lt_tilt D]
  exact ⟨D, physicalSeedDenominator_pos D,
    growthAtMost_mono hbound hgrowth⟩

#print axioms physicalSeedReciprocal_lt_tilt
#print axioms native_mertens_reciprocal_integer_seed

end RHLean.Analysis
end
