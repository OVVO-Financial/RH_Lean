import RHLean.Proof.SquareRootAmplificationPowerBounds
import RHLean.Proof.SquareRootAncestryRoot
import «research.oai_434.VF919ExplicitSlotTotalMass»

/-!
# Explicit bounds for the original historical amplification

The finite source and the complete total-mass endpoint give native Mertens
growth at `7/8 - 1/(48*N)`, where `N = explicitSlotCount` is fixed before
every integer cutoff.  This file transports that proved bound through the
exact complex/integer Mertens identity to the original endpoint ratio,
its running maximum, and its logarithmic growth ratio.

The every-positive-loss amplification boundary is `3/4 - 1/(24*N)`.
Spending half the Mertens saving gives a fixed amplification power
`3/4 - 1/(48*N)`.  Both statements retain their multiplicative constants.
The logarithmic limsup bound is an upper bound, not a zero-growth claim.
-/

namespace RHLean.Analysis

open Filter MertensExponent RHLean.Proof
open OAI.SevenEighths.Parameters OAI.SevenEighths.RHLeanExplicitSlotTotalMass

/-- The analytic and integer Mertens functions are exactly the same source. -/
theorem mertens_integer_power_of_native_power {b : ℝ}
    (hpower : MertensExponent.MertensPowerBound b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |(mertensSummatoryInt n : ℝ)| ≤ C * (n : ℝ) ^ b := by
  obtain ⟨C, hC, hbound⟩ := hpower
  refine ⟨C, hC, ?_⟩
  intro n hn
  have h := hbound n hn
  rw [← mertensSummatoryInt_cast n, Complex.norm_intCast] at h
  exact h

/-- A native Mertens power supplies one constant for every admitted cutoff. -/
theorem amplification_power_of_native_power {b : ℝ} (hb : (1 / 2 : ℝ) ≤ b)
    (hpower : MertensExponent.MertensPowerBound b) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      squareRootAmplificationMax X ≤ C * (X : ℝ) ^ (2 * b - 1) := by
  obtain ⟨C, hC, hM⟩ := mertens_integer_power_of_native_power hpower
  refine ⟨(C + 1) ^ 2, by positivity, ?_⟩
  intro X hX
  exact squareRootAmplificationMax_le_of_mertensPower hb hC hM X hX

/-- Keep the actual logarithmic constant before taking an eventual bound. -/
theorem amplification_log_bound_of_native_power {b : ℝ} (hb : (1 / 2 : ℝ) ≤ b)
    (hpower : MertensExponent.MertensPowerBound b) :
    ∃ B : ℝ, 1 < B ∧ ∀ X : ℕ, 2 ≤ X →
      squareRootAmplificationLogRatio X ≤
        2 * b - 1 + Real.log B / Real.log (X : ℝ) := by
  obtain ⟨C, hC, hM⟩ := mertens_integer_power_of_native_power hpower
  refine ⟨1 + (C + 1) ^ 2, by nlinarith only [hC, sq_nonneg C], ?_⟩
  intro X hX
  exact squareRootAmplificationLogRatio_le_of_mertensPower hb hC hM X hX

/-- Split the requested tolerance between the Mertens loss and the log constant. -/
theorem amplification_log_eventually_le_of_native_growth {b : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hgrowth : MertensGrowthAtMost b)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ X : ℕ in atTop,
      squareRootAmplificationLogRatio X ≤ 2 * b - 1 + eps := by
  obtain ⟨C, hC, hM⟩ := mertens_integer_power_of_native_power
    (hgrowth (eps / 4) (by positivity))
  have h := squareRootAmplificationLogRatio_eventually_le_of_mertensPower
    (by linarith : (1 / 2 : ℝ) ≤ b + eps / 4) hC hM
    (eps / 2) (by positivity)
  filter_upwards [h] with X hX
  linarith only [hX]

/-- Eventual upper bounds and the proved nonnegativity control the real limsup. -/
theorem amplification_log_limsup_le_of_eventual (a : ℝ)
    (hupper : ∀ eps : ℝ, 0 < eps →
      ∀ᶠ X : ℕ in atTop, squareRootAmplificationLogRatio X ≤ a + eps) :
    Filter.limsup squareRootAmplificationLogRatio atTop ≤ a := by
  have hnonneg : ∀ᶠ X : ℕ in atTop,
      0 ≤ squareRootAmplificationLogRatio X := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
    exact squareRootAmplificationLogRatio_nonneg hX
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      squareRootAmplificationLogRatio :=
    Filter.isCoboundedUnder_le_of_eventually_le atTop hnonneg
  by_contra hn
  have hlt : a < Filter.limsup squareRootAmplificationLogRatio atTop :=
    lt_of_not_ge hn
  have hb := Filter.limsup_le_of_le hcobdd
    (hupper ((Filter.limsup squareRootAmplificationLogRatio atTop - a) / 2)
      (by linarith))
  linarith only [hb, hlt]

/-- General native Mertens growth controls the original logarithmic limsup. -/
theorem amplification_log_limsup_le_of_native_growth {b : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hgrowth : MertensGrowthAtMost b) :
    Filter.limsup squareRootAmplificationLogRatio atTop ≤ 2 * b - 1 := by
  exact amplification_log_limsup_le_of_eventual (2 * b - 1)
    (amplification_log_eventually_le_of_native_growth hb hgrowth)

/-- The exact running maximum at the explicit every-positive-loss boundary. -/
theorem native_amplification_explicit_slot_count_total_mass
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      squareRootAmplificationMax X ≤
        C * (X : ℝ) ^
          ((3 / 4 : ℝ) - 1 / (24 * (explicitSlotCount : ℝ)) + eps) := by
  have hb : (1 / 2 : ℝ) ≤
      (7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps / 2 := by
    linarith only [half_le_growth_boundary, heps]
  have h := amplification_power_of_native_power hb
    (native_mertens_explicit_slot_count_total_mass (eps / 2) (by positivity))
  have hexp :
      2 * ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) + eps / 2) - 1 =
        (3 / 4 : ℝ) - 1 / (24 * (explicitSlotCount : ℝ)) + eps := by ring
  simpa only [hexp] using h

/-- A fixed no-loss power after spending half of the explicit Mertens saving. -/
theorem native_amplification_fixed_explicit_slot_count_total_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      squareRootAmplificationMax X ≤
        C * (X : ℝ) ^
          ((3 / 4 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ))) := by
  have h := amplification_power_of_native_power half_le_fixed_boundary
    native_mertens_fixed_explicit_slot_count_total_mass
  have hexp :
      2 * ((7 / 8 : ℝ) - 1 / (96 * (explicitSlotCount : ℝ))) - 1 =
        (3 / 4 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) := by ring
  simpa only [hexp] using h

/-- The finite logarithmic correction is explicit at the fixed power. -/
theorem native_amplification_log_fixed_explicit_slot_count_total_mass :
    ∃ B : ℝ, 1 < B ∧ ∀ X : ℕ, 2 ≤ X →
      squareRootAmplificationLogRatio X ≤
        (3 / 4 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) +
          Real.log B / Real.log (X : ℝ) := by
  have h := amplification_log_bound_of_native_power half_le_fixed_boundary
    native_mertens_fixed_explicit_slot_count_total_mass
  have hexp :
      2 * ((7 / 8 : ℝ) - 1 / (96 * (explicitSlotCount : ℝ))) - 1 =
        (3 / 4 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ)) := by ring
  simpa only [hexp] using h

/-- Every positive tolerance holds eventually for the user's exact ratio. -/
theorem native_amplification_log_explicit_slot_count_total_mass
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ X : ℕ in atTop,
      squareRootAmplificationLogRatio X ≤
        (3 / 4 : ℝ) - 1 / (24 * (explicitSlotCount : ℝ)) + eps := by
  have h := amplification_log_eventually_le_of_native_growth
    half_le_growth_boundary native_mertens_explicit_slot_count_total_mass eps heps
  have hexp :
      2 * ((7 / 8 : ℝ) - 1 / (48 * (explicitSlotCount : ℝ))) - 1 =
        (3 / 4 : ℝ) - 1 / (24 * (explicitSlotCount : ℝ)) := by ring
  simpa only [hexp] using h

/-- The explicit finite source gives a strict improvement in the limsup bound. -/
theorem native_amplification_limsup_explicit_slot_count_total_mass :
    Filter.limsup squareRootAmplificationLogRatio atTop ≤
      (3 / 4 : ℝ) - 1 / (24 * (explicitSlotCount : ℝ)) := by
  exact amplification_log_limsup_le_of_eventual _
    native_amplification_log_explicit_slot_count_total_mass

/-- In particular, the bound for the exact logarithmic limsup is below three quarters. -/
theorem native_amplification_limsup_lt_three_quarters :
    Filter.limsup squareRootAmplificationLogRatio atTop < (3 / 4 : ℝ) := by
  have hgain : 0 < (1 : ℝ) / (24 * (explicitSlotCount : ℝ)) :=
    div_pos zero_lt_one (mul_pos (by norm_num) slot_count_cast_pos)
  linarith only [native_amplification_limsup_explicit_slot_count_total_mass, hgain]

/-- The original amplification maximum is eventually strictly below its cutoff. -/
theorem native_amplification_eventually_lt_cutoff :
    ∀ᶠ X : ℕ in atTop, squareRootAmplificationMax X < (X : ℝ) := by
  obtain ⟨C, hC, hM⟩ := mertens_integer_power_of_native_power
    native_mertens_fixed_explicit_slot_count_total_mass
  exact squareRootAmplificationMax_eventually_lt_of_mertensPower
    half_le_fixed_boundary fixed_boundary_lt_one hC hM

#print axioms native_amplification_explicit_slot_count_total_mass
#print axioms native_amplification_fixed_explicit_slot_count_total_mass
#print axioms native_amplification_log_fixed_explicit_slot_count_total_mass
#print axioms native_amplification_log_explicit_slot_count_total_mass
#print axioms native_amplification_limsup_explicit_slot_count_total_mass
#print axioms native_amplification_limsup_lt_three_quarters
#print axioms native_amplification_eventually_lt_cutoff

end RHLean.Analysis
