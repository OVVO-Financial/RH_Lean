import «research.oai_434.VF919TotalMassEndpoint»
import «research.oai_434.VF919ExplicitFixedSourceSlotCount»

/-!
# Reclaim the exact OAI HIGH window reserve in the LOW/principal comparison

The existing complete signed total-slot-mass LOW theorem has the physical
power 3/16 - 9*h. The principal signal power shifts by -8*h, so the
certified LOW-to-principal gain is exactly h. The preceding endpoint
calibrated the original fixed source with sigma=m/4 for m=actualSlotMinimum.

However the actual unchanged HIGH proof requires
  sigma + e <= (7/8)*((7/8)*rmin),
and the same source has e <= ((7/8)*rmin)/4.
After the already-proved exact minimum rmin calibration, this permits
  sigma=(7/8)*actualSlotMinimum-e >= 5*actualSlotMinimum/8.

This file changes only the source DATA CERTIFICATE's sigma, not the actual
physical slots, detector error e, moments, compensated probe, analytic
phases, prime masks, or principal normalizer. The ORIGINAL HIGH supplier
is reused and all HighData budget fields are reverified individually.

No assumptions on RH, Mertens, signed covariance or future source moments.
The original pinned analytic proof is still the separately compiled input.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.RHLeanWindowSaturated

open Parameters RHLeanFiniteSlotGap RHLeanActualSlotMin
open RHLeanNativeSevenEighthsReplay RHLeanFullPhysicalTilt
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands

/-- Reallocate the unused original HIGH window capacity to sigma. Keep
every original source-relevant field apart from sigma unchanged. -/
noncomputable def windowSaturatedHighData {Delta : ℝ}
    (D : HighData Delta) : HighData Delta := by
  let E := cappedHighData D
  let m : ℝ := (7 / 8 : ℝ) * E.rmin
  let newSigma : ℝ := (7 / 8 : ℝ) * m - E.e
  have hm : 0 < m := by
    dsimp [m]
    exact mul_pos (by norm_num) E.rmin_pos
  have hslot := E.slots_bounds ⟨0, E.slots_pos⟩
  have hmT : m ≤ E.t / 200 := by
    dsimp [m]
    linarith only [hslot.2.1, hslot.2.2]
  have hs := capped_high_data_bounds D
  change E.ε ≤ E.t / 2000 ∧ E.e ≤ E.t / 2000 ∧
    ((E.N : ℝ) + 8) * E.eps ≤ E.t ∧
    E.sigma ≤ m / 4 ∧ E.e ≤ m / 4 at hs
  have heT : E.e ≤ E.t / 2000 := hs.2.1
  have heN : ((E.N : ℝ) + 8) * E.eps ≤ E.t := hs.2.2.1
  have heM : E.e ≤ m / 4 := hs.2.2.2.2
  have hnewpos : 0 < newSigma := by
    dsimp [newSigma]
    linarith only [hm, heM]
  refine { E with
    sigma := newSigma
    sigma_pos := hnewpos
    geometric_budget := ?_
    principal_budget := ?_
    window_budget := ?_
    floor_budget := ?_
    high_saving := ?_ }
  · dsimp only [newSigma]
    linarith only [hmT, heT, E.t_small, E.e_pos, E.t_pos]
  · dsimp only [newSigma]
    linarith only [hmT, E.t_small, E.e_pos, E.t_pos]
  · dsimp [newSigma, m]
    ring
  · dsimp only [newSigma]
    linarith only [hmT, heT, heN, E.t_small, E.e_pos, E.t_pos]
  · dsimp only [newSigma]
    linarith only [hmT, E.e_pos, E.t_pos]

/-- The complete original physical geometry and detector error are unchanged. -/
theorem windowSaturatedHighData_geometry {Delta : ℝ} (D : HighData Delta) :
    (windowSaturatedHighData D).t = D.t ∧
    (windowSaturatedHighData D).N = D.N ∧
    (windowSaturatedHighData D).ell = D.ell ∧
    (windowSaturatedHighData D).rmin = D.rmin ∧
    (windowSaturatedHighData D).e = D.e := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The original complete HIGH window condition is now an equality rather
than leaving a quarter-slot certificate in reserve. -/
theorem windowSaturatedHighData_window_exact {Delta : ℝ}
    (D : HighData Delta) :
    (windowSaturatedHighData D).sigma +
      (windowSaturatedHighData D).e =
      (7 / 8 : ℝ) * ((7 / 8 : ℝ) * (windowSaturatedHighData D).rmin) := by
  change ((7 / 8 : ℝ) * ((7 / 8 : ℝ) * (cappedHighData D).rmin) -
    (cappedHighData D).e) + (cappedHighData D).e =
      (7 / 8 : ℝ) * ((7 / 8 : ℝ) * (cappedHighData D).rmin)
  ring

/-- The same source's actual error e and exact slot minimum determine
the full spare HIGH reserve. -/
theorem windowSaturatedHighData_sigma_exact_minimum {Delta : ℝ}
    (D : HighData Delta) :
    (windowSaturatedHighData (sourceWithExactSlotMinimum D)).sigma =
      (7 / 8 : ℝ) * actualSlotMinimum D - D.e := by
  change ((7 / 8 : ℝ) * ((7 / 8 : ℝ) * trueMinimumRmin D) - D.e) =
    (7 / 8 : ℝ) * actualSlotMinimum D - D.e
  rw [trueMinimumRmin_exact D]

/-- The actual positive detector error costs at most a quarter of the
unchanged minimum slot. Thus full window use gains >= 5*m/8. -/
theorem windowSaturatedHighData_sigma_ge_five_eighths {Delta : ℝ}
    (D : HighData Delta) :
    (5 / 8 : ℝ) * actualSlotMinimum D ≤
      (windowSaturatedHighData (sourceWithExactSlotMinimum D)).sigma := by
  have he := (capped_high_data_bounds
    (sourceWithExactSlotMinimum D)).2.2.2.2
  change D.e ≤ ((7 / 8 : ℝ) * trueMinimumRmin D) / 4 at he
  rw [trueMinimumRmin_exact D] at he
  rw [windowSaturatedHighData_sigma_exact_minimum D]
  linarith only [he]

/-- Replacing sigma by the window-saturated value still stays strictly
inside the physical tilt and OAI large-tail constraints. -/
theorem windowSaturatedHighData_tilt_budget {Delta : ℝ}
    (D : HighData Delta) :
    let E := windowSaturatedHighData (sourceWithExactSlotMinimum D)
    0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t := by
  let E := windowSaturatedHighData (sourceWithExactSlotMinimum D)
  change 0 < E.sigma ∧ E.sigma < 1 / 960 ∧ 24 * E.sigma < E.t
  have hmin : actualSlotMinimum D ≤ D.t / 200 := by
    have h := (D.slots_bounds (leastSlotIndex D)).2.2
    change D.ell (leastSlotIndex D) ≤ D.t / 200 at h
    exact h
  have hσ := windowSaturatedHighData_sigma_exact_minimum D
  change E.sigma = (7 / 8 : ℝ) * actualSlotMinimum D - D.e at hσ
  refine ⟨E.sigma_pos, ?_, ?_⟩
  · rw [hσ]
    linarith only [hmin, D.t_small, D.e_pos, D.t_pos]
  · rw [hσ]
    change 24 * ((7 / 8 : ℝ) * actualSlotMinimum D - D.e) < D.t
    linarith only [hmin, D.t_pos, D.e_pos]

/-- COMPLETE original OAI LOW/HIGH/principal comparison with the new
window-saturated sigma on the same physical coefficient source. -/
theorem native_beta_le_window_saturated_minimum_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    HeckeZeroSupremum.beta ≤
      7 / 8 - ((7 / 8 : ℝ) * actualSlotMinimum D - D.e) := by
  let Dstar := sourceWithExactSlotMinimum D
  let E := windowSaturatedHighData Dstar
  have hfineE : ∀ i, E.ell i ≤
      detectorMesh (1 / 1000000) E.t / 200 := by
    exact hfine
  have hepsilon : E.ε ≤ E.t / 2000 :=
    (capped_high_data_bounds Dstar).1
  have he : E.e ≤ E.t / 2000 :=
    (capped_high_data_bounds Dstar).2.1
  have heps : ((E.N : ℝ) + 8) * E.eps ≤ E.t :=
    (capped_high_data_bounds Dstar).2.2.1
  obtain ⟨hpos, hsmall, htail⟩ :=
    windowSaturatedHighData_tilt_budget D
  obtain ⟨F⟩ := exists_source_data E
  obtain ⟨counts⟩ := source_count_parameters F
  have hbound := native_beta_le_total_mass_boundary
    E E.sigma hpos hsmall htail hfineE hepsilon he heps le_rfl F counts
  rw [windowSaturatedHighData_sigma_exact_minimum D] at hbound
  exact hbound

/-- Stronger true-Mobius exponent without a new arithmetic cancellation
hypothesis, retaining the ORIGINAL e and all explicit OAI HIGH constraints. -/
theorem native_beta_le_window_saturated_five_eighths_of_fine
    (D : HighData (1 / 1000000 : ℝ))
    (hfine : ∀ i, D.ell i ≤ detectorMesh (1 / 1000000) D.t / 200) :
    HeckeZeroSupremum.beta ≤ 7 / 8 - (5 / 8 : ℝ) * actualSlotMinimum D := by
  have hbound := native_beta_le_window_saturated_minimum_of_fine D hfine
  have he := (capped_high_data_bounds
    (sourceWithExactSlotMinimum D)).2.2.2.2
  change D.e ≤ ((7 / 8 : ℝ) * trueMinimumRmin D) / 4 at he
  rw [trueMinimumRmin_exact D] at he
  linarith only [hbound, he]

/-- One actual source fixed before any zero, character or loss. -/
theorem native_beta_le_window_saturated_five_eighths :
    ∃ D : HighData (1 / 1000000 : ℝ),
      0 < actualSlotMinimum D ∧
      HeckeZeroSupremum.beta ≤
        7 / 8 - (5 / 8 : ℝ) * actualSlotMinimum D := by
  obtain ⟨D, hfine⟩ :=
    Parameters.exists_high_data_fine (1 / 1000000) (by norm_num)
      (detectorMesh (1 / 1000000))
      (fun t ht => detectorMesh_pos (by norm_num) ht)
  exact ⟨D, actualSlotMinimum_pos D,
    native_beta_le_window_saturated_five_eighths_of_fine D hfine⟩

/-- Explicit fixed-constant exponent gain.  The constructed source from
VF919ExplicitFixedSourceSlotCount already supplies m >= 1/(12*N_*). -/
theorem native_beta_le_explicit_window_saturated :
    HeckeZeroSupremum.beta ≤
      (7 / 8 : ℝ) - (5 : ℝ) / (96 * (explicitSlotCount : ℝ)) := by
  obtain ⟨D, hfine, hslotLower, _hN, _ht⟩ :=
    Parameters.exists_explicit_high_data_fine
  have hbound := native_beta_le_window_saturated_five_eighths_of_fine D hfine
  have hmin : (1 : ℝ) / (12 * (explicitSlotCount : ℝ)) ≤
      actualSlotMinimum D := hslotLower (leastSlotIndex D)
  have hident : (5 : ℝ) / (96 * (explicitSlotCount : ℝ)) =
      (5 / 8 : ℝ) * ((1 : ℝ) / (12 * (explicitSlotCount : ℝ))) := by ring
  rw [hident]
  linarith only [hbound, hmin]

#print axioms windowSaturatedHighData
#print axioms windowSaturatedHighData_window_exact
#print axioms native_beta_le_window_saturated_minimum_of_fine
#print axioms native_beta_le_explicit_window_saturated

end SevenEighths.RHLeanWindowSaturated
end
end OAI

namespace RHLean.Analysis
open MertensExponent OAI.SevenEighths
open OAI.SevenEighths.RHLeanWindowSaturated
open OAI.SevenEighths.RHLeanNativeSevenEighthsReplay
open OAI.SevenEighths.Parameters

/-- Original integer Mobius partial sums inherit the new fixed, uniform
OAI exponent, with an arbitrary positive loss and no cutoff assumptions. -/
theorem native_mertens_explicit_window_saturated :
    MertensGrowthAtMost
      ((7 / 8 : ℝ) - (5 : ℝ) / (96 * (explicitSlotCount : ℝ))) := by
  exact growthAtMost_mono
    native_beta_le_explicit_window_saturated
    native_mertens_growth_at_hecke_beta

#print axioms native_mertens_explicit_window_saturated

end RHLean.Analysis
