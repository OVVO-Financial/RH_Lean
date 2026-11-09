import «research.oai_434.VF919WindowSaturatedLowPrincipal»
import «research.oai_434.VF919ExplicitSquareBlockPacking»

/-!
# Close the positive detector-error loss in the complete OAI endpoint

Claims 20261108-analytic-3/EC1-EC3, independently accepted with scope by
20261108-referee-3. Every positive smaller error admits a valid original
HighData record. The complete window-saturated theorem constructs a fresh
finite source for that record, including its stronger FirstTail allowance.
Only its numerical inequality for the same beta is closed. No zero-error
source, fixed old exclusion mask, or uniform analytic limit is asserted.
-/

namespace OAI
noncomputable section
namespace SevenEighths.RHLeanWindowSaturated

open Parameters RHLeanActualSlotMin ProbeFinalAssemblyCertifiedBands

/-- Decrease only the positive detector error; recertify every affected budget. -/
def withSmallerError {Delta : ℝ} (D : HighData Delta)
    (e : ℝ) (he : 0 < e) (hle : e ≤ D.e) : HighData Delta := by
  refine { D with
    e := e
    e_pos := he
    e_small := hle.trans_lt D.e_small
    detector_budget := ?_
    phase_budget := ?_
    central_budget := ?_
    geometric_budget := ?_
    window_budget := ?_
    floor_budget := ?_ }
  · linarith only [D.detector_budget, hle]
  · have ht := mul_le_mul_of_nonneg_right hle D.t_pos.le
    linarith only [D.phase_budget, ht]
  · linarith only [D.central_budget, hle]
  · linarith only [D.geometric_budget, hle]
  · linarith only [D.window_budget, hle]
  · linarith only [D.floor_budget, hle]

/-- The fixed slot geometry, original reserve and positive new error are explicit. -/
theorem withSmallerError_geometry {Delta : ℝ} (D : HighData Delta)
    (e : ℝ) (he : 0 < e) (hle : e ≤ D.e) :
    (withSmallerError D e he hle).t = D.t ∧
    (withSmallerError D e he hle).N = D.N ∧
    (withSmallerError D e he hle).ell = D.ell ∧
    (withSmallerError D e he hle).sigma = D.sigma ∧
    (withSmallerError D e he hle).e = e := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Compare minimum values, without identifying arbitrary chosen minimum indices. -/
theorem withSmallerError_minimum {Delta : ℝ} (D : HighData Delta)
    (e : ℝ) (he : 0 < e) (hle : e ≤ D.e) :
    actualSlotMinimum (withSmallerError D e he hle) = actualSlotMinimum D := by
  apply le_antisymm
  · exact leastSlotIndex_le (withSmallerError D e he hle) (leastSlotIndex D)
  · exact leastSlotIndex_le D (leastSlotIndex (withSmallerError D e he hle))

/-- Complete fixed-geometry boundary. Each invocation of the input theorem
reconstructs SourceData and counts at its own strictly positive error. -/
theorem native_beta_le_window_error_closed_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    HeckeZeroSupremum.beta ≤ 7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D := by
  by_contra h
  have hgap : 0 < HeckeZeroSupremum.beta -
      (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D) :=
    sub_pos.mpr (lt_of_not_ge h)
  let e : ℝ := min D.e ((HeckeZeroSupremum.beta -
    (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D)) / 2)
  have he : 0 < e := lt_min D.e_pos (half_pos hgap)
  have hle : e ≤ D.e := min_le_left _ _
  have hhalf : e ≤ (HeckeZeroSupremum.beta -
      (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D)) / 2 := min_le_right _ _
  let E := withSmallerError D e he hle
  have hfineE : ∀ i, E.ell i ≤ detectorMesh (1 / 1000000) E.t / 200 := hfine
  have hbound := native_beta_le_window_saturated_minimum_of_fine E hfineE
  have hminimum : actualSlotMinimum E = actualSlotMinimum D :=
    withSmallerError_minimum D e he hle
  change HeckeZeroSupremum.beta ≤
    7 / 8 - ((7 / 8 : ℝ) * actualSlotMinimum E - e) at hbound
  rw [hminimum] at hbound
  linarith only [hbound, hhalf, hgap]

/-- Use the already fixed near-uniform source, without optimizing its slot count. -/
theorem native_beta_le_near_uniform_window_error_closed :
    HeckeZeroSupremum.beta ≤
      (7 / 8 : ℝ) - (7 : ℝ) / (64 * (nearUniformSlotCount : ℝ)) := by
  obtain ⟨D, hfine, hslotLower, _hN, _ht⟩ := exists_near_uniform_high_data_fine
  have hbound := native_beta_le_window_error_closed_of_fine D hfine
  have hmin : (1 : ℝ) / (8 * (nearUniformSlotCount : ℝ)) ≤
      actualSlotMinimum D := hslotLower (leastSlotIndex D)
  have hscale := mul_le_mul_of_nonneg_left hmin (by norm_num : (0 : ℝ) ≤ 7 / 8)
  have hident : (7 / 8 : ℝ) * ((1 : ℝ) / (8 * (nearUniformSlotCount : ℝ))) =
      (7 : ℝ) / (64 * (nearUniformSlotCount : ℝ)) := by ring
  rw [hident] at hscale
  exact hbound.trans (sub_le_sub_left hscale (7 / 8 : ℝ))

end SevenEighths.RHLeanWindowSaturated
end
end OAI

namespace RHLean.Analysis

open MertensExponent OAI.SevenEighths
open Parameters RHLeanActualSlotMin RHLeanWindowSaturated
open RHLeanNativeSevenEighthsReplay ProbeFinalAssemblyCertifiedBands

/-- Every positive exponent loss is retained on the genuine Mobius source. -/
theorem native_mertens_window_error_closed_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    MertensGrowthAtMost (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D) := by
  exact growthAtMost_mono (native_beta_le_window_error_closed_of_fine D hfine)
    native_mertens_growth_at_hecke_beta

/-- Spend half the removed error to beat the previous exact same-D ceiling
with a single fixed power, rather than dropping a positive exponent loss. -/
theorem native_mertens_fixed_window_error_closed_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    MertensPowerBound (7 / 8 - (7 / 8 : ℝ) * actualSlotMinimum D + D.e / 2) := by
  exact native_mertens_window_error_closed_of_fine D hfine (D.e / 2)
    (half_pos D.e_pos)

/-- Explicit fixed-family every-positive-loss consequence. -/
theorem native_mertens_near_uniform_window_error_closed :
    MertensGrowthAtMost
      ((7 / 8 : ℝ) - (7 : ℝ) / (64 * (nearUniformSlotCount : ℝ))) := by
  exact growthAtMost_mono native_beta_le_near_uniform_window_error_closed
    native_mertens_growth_at_hecke_beta

end RHLean.Analysis
